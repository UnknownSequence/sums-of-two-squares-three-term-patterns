import TriplesFinal.TypeIProof.BlockRem

/-!
# The main terms on the annuli `R < |t| ≤ R₁` (the tail `|t| > T₁`)

For large `|t|` the main terms `B^±` are bounded trivially (Cauchy–Schwarz over `h`), using the
decay `|M_h(iτ)| ≤ C_k (1 + |τ|)^(-k)` (Lemma 11.3) and the large sieve inequality with a single
coefficient: `∫_{R < |t| ≤ R₁} m_main ≤ (X/K)² Y^(-1) (7/4) · 2M (C_k (1+R)^(-k))² ·
2M C(η)(R₁² + M^(1+η)/q)`.

Paper: §12.3.
-/

namespace Triples

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff Interval

namespace Setup

variable {Cν : ℕ → ℝ} (S : Setup Cν) (ψ₀ : DyadicPartition) (F : SpecFam)

theorem norm_phiT_le_Mh (τ : ℝ) {h : ℝ} (hh : 0 < h) :
    ‖S.phiT ψ₀ τ h‖ ≤ ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (I * τ)‖ := by
  unfold phiT
  rw [RCLike.norm_conj, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (ψ₀.nonneg _), S.norm_cpow_piY τ hh, mul_one]
  have h1 := ψ₀.le_one (h / S.M)
  calc ψ₀.ψ₀ (h / S.M) * ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (I * τ)‖
      ≤ 1 * ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (I * τ)‖ := by gcongr
    _ = _ := one_mul _

/-- `m_main(ρ_t, ±t)` is integrable on annuli in the real spectrum. -/
theorem integrableOn_mMain {R₀ R₁ : ℝ} (hR₀ : 1 / 2 ≤ R₀) {sg : ℝ} (hsg : sg = 1 ∨ sg = -1) :
    IntegrableOn (fun x => S.mMain ψ₀ (F.ρ x) (sg * (F.t x).re)) (F.annulus R₀ R₁) F.ν := by
  have hAm := F.measurableSet_annulus R₀ R₁
  have hτm : Measurable fun x => sg * (F.t x).re :=
    measurable_const.mul (Complex.measurable_re.comp F.meas_t)
  have hsq := F.integrableOn_sq_sum S.Hs (c := fun x n => S.phiT ψ₀ (sg * (F.t x).re) n)
    (fun n => S.measurable_phiT_comp ψ₀ F hτm n) (fun x n => S.norm_phiT_le ψ₀ _ _) R₁
  have h1 := ((F.integrableOn_div_ch hsq).mono_set (F.annulus_subset_ball R₀ R₁)).const_mul
    (S.Bk ^ 2 * (7 / 4))
  refine IntegrableOn.congr_fun h1 (fun x hx => ?_) hAm
  have hx' : x ∉ F.exc := F.not_exc_of_mem_annulus hR₀ hx
  have hch : F.ch x = Real.cosh (Real.pi * (sg * (F.t x).re)) := by
    rw [F.ch_of_not_exc hx']
    rcases hsg with h | h
    · simp [h]
    · rw [← Real.cosh_neg (Real.pi * (sg * (F.t x).re))]; congr 1; simp [h]
  unfold mMain
  rw [hch]
  simp only [mul_comm (S.phiT ψ₀ _ _) (F.ρ x _)]
  ring

set_option maxHeartbeats 1000000 in
/-- **The main terms on the annulus `R < |t| ≤ R₁`**, bounded trivially. -/
theorem tail_block {Cls : ℝ → ℝ} (hLS : F.LS S.q Cls) {k : ℝ} (hk : 0 ≤ k) {Ck : ℝ}
    (hCk : 0 ≤ Ck)
    (hMk : ∀ h ∈ S.Hs, ∀ τ : ℝ, ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (I * τ)‖ ≤ Ck * (1 + |τ|) ^ (-k))
    {R R₁ : ℝ} (hR : 1 ≤ R) (hR₁ : 1 ≤ R₁) {sg : ℝ} (hsg : sg = 1 ∨ sg = -1) :
    IntegrableOn (fun x => S.mMain ψ₀ (F.ρ x) (sg * (F.t x).re)) (F.annulus R R₁) F.ν ∧
    ∫ x in F.annulus R R₁, S.mMain ψ₀ (F.ρ x) (sg * (F.t x).re) ∂F.ν ≤
      S.Bk ^ 2 * (7 / 4) * (2 * S.M * (Ck * (1 + R) ^ (-k)) ^ 2) *
        (2 * S.M * (Cls S.η * (R₁ ^ 2 + S.M ^ (1 + S.η) / S.q))) := by
  classical
  have hM := S.M_pos
  have hq := S.q_pos
  set A := F.annulus R R₁ with hA
  have hAm : MeasurableSet A := F.measurableSet_annulus R R₁
  have hint := S.integrableOn_mMain ψ₀ F (R₀ := R) (R₁ := R₁) (by linarith) hsg
  refine ⟨hint, ?_⟩
  set K : ℝ := S.Bk ^ 2 * (7 / 4) * (2 * S.M * (Ck * (1 + R) ^ (-k)) ^ 2) with hK
  have hK0 : 0 ≤ K := by positivity
  -- the pointwise bound
  have hpt : ∀ x ∈ A, S.mMain ψ₀ (F.ρ x) (sg * (F.t x).re) ≤
      K * ((∑ h ∈ S.Hs, ‖F.ρ x h‖ ^ 2) / F.ch x) := by
    intro x hx
    have hx' : x ∉ F.exc := F.not_exc_of_mem_annulus (by linarith) hx
    have hτ : R < |sg * (F.t x).re| := by
      have : |sg * (F.t x).re| = |(F.t x).re| := by
        rw [abs_mul]; rcases hsg with h | h <;> simp [h]
      rw [this, ← F.norm_eq_abs_re_of_not_exc hx']; exact hx.1
    have hch : F.ch x = Real.cosh (Real.pi * (sg * (F.t x).re)) := by
      rw [F.ch_of_not_exc hx']
      rcases hsg with h | h
      · simp [h]
      · rw [← Real.cosh_neg (Real.pi * (sg * (F.t x).re))]; congr 1; simp [h]
    have hφ : ∀ h ∈ S.Hs, ‖S.phiT ψ₀ (sg * (F.t x).re) h‖ ≤ Ck * (1 + R) ^ (-k) := by
      intro h hh
      have hh0 : (0 : ℝ) < h := by
        have := (S.le_of_mem_Hs hh).1; exact_mod_cast this
      refine (S.norm_phiT_le_Mh ψ₀ _ hh0).trans ((hMk h hh _).trans ?_)
      apply mul_le_mul_of_nonneg_left _ hCk
      exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    have hsum : ‖∑ h ∈ S.Hs, F.ρ x h * S.phiT ψ₀ (sg * (F.t x).re) h‖ ^ 2 ≤
        2 * S.M * (Ck * (1 + R) ^ (-k)) ^ 2 * ∑ h ∈ S.Hs, ‖F.ρ x h‖ ^ 2 := by
      refine (SpecFam.sq_norm_sum_le S.Hs _).trans ?_
      have h2 : ∑ h ∈ S.Hs, ‖F.ρ x h * S.phiT ψ₀ (sg * (F.t x).re) h‖ ^ 2 ≤
          (Ck * (1 + R) ^ (-k)) ^ 2 * ∑ h ∈ S.Hs, ‖F.ρ x h‖ ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro h hh
        rw [norm_mul, mul_pow, mul_comm]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) (hφ h hh) 2) (sq_nonneg _)
      calc ((S.Hs).card : ℝ) * ∑ h ∈ S.Hs, ‖F.ρ x h * S.phiT ψ₀ (sg * (F.t x).re) h‖ ^ 2
          ≤ (2 * S.M) * ((Ck * (1 + R) ^ (-k)) ^ 2 * ∑ h ∈ S.Hs, ‖F.ρ x h‖ ^ 2) :=
            mul_le_mul S.card_Hs_le h2 (Finset.sum_nonneg fun _ _ => sq_nonneg _)
              (by linarith)
        _ = _ := by ring
    unfold mMain
    rw [← hch, hK]
    have hc := F.ch_pos x
    rw [div_mul_eq_mul_div, div_le_iff₀ hc]
    have : S.Bk ^ 2 * (7 / 4) * (2 * S.M * (Ck * (1 + R) ^ (-k)) ^ 2) *
        ((∑ h ∈ S.Hs, ‖F.ρ x h‖ ^ 2) / F.ch x) * F.ch x =
        S.Bk ^ 2 * (7 / 4) * (2 * S.M * (Ck * (1 + R) ^ (-k)) ^ 2 *
          ∑ h ∈ S.Hs, ‖F.ρ x h‖ ^ 2) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  -- integrating
  have hρi : ∀ h, IntegrableOn (fun x => ‖F.ρ x h‖ ^ 2 / F.ch x) (F.ball R₁) F.ν :=
    fun h => F.integrableOn_div_ch (F.intρ h R₁)
  have hsumi : IntegrableOn (fun x => (∑ h ∈ S.Hs, ‖F.ρ x h‖ ^ 2) / F.ch x) A F.ν :=
    (F.integrableOn_div_ch (F.integrableOn_sum_sq_ρ S.Hs R₁)).mono_set
      (F.annulus_subset_ball R R₁)
  calc ∫ x in A, S.mMain ψ₀ (F.ρ x) (sg * (F.t x).re) ∂F.ν
      ≤ ∫ x in A, K * ((∑ h ∈ S.Hs, ‖F.ρ x h‖ ^ 2) / F.ch x) ∂F.ν :=
        setIntegral_mono_on hint (hsumi.const_mul K) hAm hpt
    _ = K * ∑ h ∈ S.Hs, ∫ x in A, ‖F.ρ x h‖ ^ 2 / F.ch x ∂F.ν := by
        rw [integral_const_mul]
        congr 1
        rw [← integral_finsetSum _ (fun h _ =>
          (hρi h).mono_set (F.annulus_subset_ball R R₁))]
        congr 1
        funext x
        rw [Finset.sum_div]
    _ ≤ K * ∑ h ∈ S.Hs, Cls S.η * (R₁ ^ 2 + ((h : ℝ) / 2) ^ (1 + S.η) / S.q) := by
        apply mul_le_mul_of_nonneg_left _ hK0
        apply Finset.sum_le_sum
        intro h hh
        calc ∫ x in A, ‖F.ρ x h‖ ^ 2 / F.ch x ∂F.ν
            ≤ ∫ x in F.ball R₁, ‖F.ρ x h‖ ^ 2 / F.ch x ∂F.ν :=
              setIntegral_mono_set (hρi h)
                (Eventually.of_forall fun x => div_nonneg (sq_nonneg _) (F.ch_pos x).le)
                (Eventually.of_forall (F.annulus_subset_ball R R₁))
          _ ≤ _ := S.LS_single F hLS (S.le_of_mem_Hs hh).1 hR₁
    _ ≤ K * (2 * S.M * (Cls S.η * (R₁ ^ 2 + S.M ^ (1 + S.η) / S.q))) := by
        apply mul_le_mul_of_nonneg_left _ hK0
        have hC := S.Cls_nonneg F hLS
        calc ∑ h ∈ S.Hs, Cls S.η * (R₁ ^ 2 + ((h : ℝ) / 2) ^ (1 + S.η) / S.q)
            ≤ ∑ _h ∈ S.Hs, Cls S.η * (R₁ ^ 2 + S.M ^ (1 + S.η) / S.q) := by
              apply Finset.sum_le_sum
              intro h hh
              apply mul_le_mul_of_nonneg_left _ hC
              have h2 := (S.le_of_mem_Hs hh).2
              have h3 : (h : ℝ) / 2 ≤ S.M := by linarith
              have h4 : ((h : ℝ) / 2) ^ (1 + S.η) ≤ S.M ^ (1 + S.η) :=
                Real.rpow_le_rpow (by positivity) h3 (by linarith [S.hη])
              gcongr
          _ = ((S.Hs).card : ℝ) * (Cls S.η * (R₁ ^ 2 + S.M ^ (1 + S.η) / S.q)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ _ := mul_le_mul_of_nonneg_right S.card_Hs_le (mul_nonneg hC (by positivity))
    _ = _ := by rw [hK]

end Setup

end Triples
