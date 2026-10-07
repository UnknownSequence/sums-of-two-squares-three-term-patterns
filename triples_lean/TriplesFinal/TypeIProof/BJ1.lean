import TriplesFinal.TypeIProof.BJ0

/-!
# The coefficients `B` on the spectrum `𝒥₁`

For real `τ ≠ 0`, the Mellin–Barnes formula splits `B = B⁺ + B⁻ + Bᴿ` (`B_eq_J1`), with
`B^± = (X/K) Y^(-1/2) ½ Γ(±iτ) ∑_h ψ₀(h/M) conj(ρ(h)) (πhY)^(∓iτ) M_h(±iτ)` and
`Bᴿ = (X/K) Y^(-1/2) (1/2π) ∫ G_τ(w) D(ρ, ξ) dξ`, `D(ρ, ξ) = ∑_h ψ₀(h/M) conj(ρ(h)) (2πhY)^(-w)
M_h(w)`, `w = -3/2 + iξ`.

Paper: §§12.3–12.4.
-/

namespace Triples

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff Interval

namespace Setup

variable {Cν : ℕ → ℝ} (S : Setup Cν) (ψ₀ : DyadicPartition)

/-- `w ↦ M_h(w)` is continuous. -/
theorem continuous_Mh_w (h : ℝ) : Continuous (fun w : ℂ => Mh S.ψ₁ S.ψ₂ S.X S.K h w) := by
  have hg := S.continuous_gMh h
  have hc : Continuous (Function.uncurry fun (w : ℂ) (s : ℝ) =>
      gMh S.ψ₁ S.ψ₂ S.X S.K h s * (s : ℂ) ^ (-w)) := by
    rw [continuous_iff_continuousAt]
    rintro ⟨w, s⟩
    by_cases hs : s < 1 / 2
    · apply (continuousAt_const (y := (0 : ℂ))).congr
      have hev : ∀ᶠ p in 𝓝 (w, s), p.2 < 1 / 2 :=
        (continuous_snd.tendsto (w, s)).eventually (Iio_mem_nhds hs)
      filter_upwards [hev] with p hp
      have h0 : gMh S.ψ₁ S.ψ₂ S.X S.K h p.2 = 0 := by
        by_contra hne
        have := gMh_support S.hyp.supp₁ S.X S.K h hne
        linarith [this.1]
      simp [Function.uncurry, h0]
    · have hs0 : 0 < s := by linarith
      apply ContinuousAt.mul (hg.continuousAt.comp continuous_snd.continuousAt)
      apply ContinuousAt.cpow (by fun_prop) (by fun_prop)
      exact Complex.ofReal_mem_slitPlane.2 hs0
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc _ _

/-- `|M_h(w)| ≤ 2C₀²` for `Re w ≤ 0`. -/
theorem norm_Mh_le' (h : ℝ) {w : ℂ} (hw : w.re ≤ 0) :
    ‖Mh S.ψ₁ S.ψ₂ S.X S.K h w‖ ≤ 2 * S.C₀ ^ 2 := by
  unfold Mh
  have hle : ∀ s ∈ Ι (1 / 2 : ℝ) 1, ‖w1 S.ψ₁ s * ah S.ψ₂ S.X S.K h s * (s : ℂ) ^ (-w)‖ ≤
      4 * S.C₀ ^ 2 := by
    intro s hs
    rw [uIoc_of_le (by norm_num)] at hs
    have hs' : s ∈ Icc (1 / 2 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
    have hs0 : 0 < s := by linarith [hs.1]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hs0]
    have h1 := S.norm_gMh_le h hs'
    have h2 : s ^ (-w).re ≤ 1 := Real.rpow_le_one hs0.le hs.2 (by simp; linarith)
    have h3 : 0 ≤ s ^ (-w).re := Real.rpow_nonneg hs0.le _
    calc ‖w1 S.ψ₁ s * ah S.ψ₂ S.X S.K h s‖ * s ^ (-w).re ≤ 4 * S.C₀ ^ 2 * 1 :=
          mul_le_mul h1 h2 h3 (by have := S.C₀_nonneg; positivity)
      _ = 4 * S.C₀ ^ 2 := mul_one _
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hle).trans (le_of_eq ?_)
  rw [show |(1 : ℝ) - 1 / 2| = 1 / 2 by norm_num]
  ring

/-- `φ_τ(y) = conj(ψ₀(y/M) (πyY)^(-iτ) M_y(iτ))`, the twist of `B⁺`. -/
noncomputable def phiT (τ y : ℝ) : ℂ :=
  (starRingEnd ℂ) ((ψ₀.ψ₀ (y / S.M) : ℂ) * ((Real.pi * y * S.Y : ℝ) : ℂ) ^ (-(I * τ)) *
    Mh S.ψ₁ S.ψ₂ S.X S.K y (I * τ))

/-- `B⁺(ρ, τ) = (X/K) Y^(-1/2) ½ Γ(iτ) ∑_h ψ₀(h/M) conj(ρ(h)) (πhY)^(-iτ) M_h(iτ)`. -/
noncomputable def Bmain (ρ : ℕ → ℂ) (τ : ℝ) : ℂ :=
  (S.Bk : ℂ) * ((1 / 2 : ℂ) * Complex.Gamma (I * τ) *
    ∑ h ∈ S.Hs, (ψ₀.ψ₀ (h / S.M) : ℂ) * (starRingEnd ℂ) (ρ h) *
      ((Real.pi * h * S.Y : ℝ) : ℂ) ^ (-(I * τ)) * Mh S.ψ₁ S.ψ₂ S.X S.K h (I * τ))

/-- `D(ρ, ξ) = ∑_h ψ₀(h/M) conj(ρ(h)) (2πhY)^(-w) M_h(w)`, `w = -3/2 + iξ`. -/
noncomputable def Dsum (ρ : ℕ → ℂ) (ξ : ℝ) : ℂ :=
  ∑ h ∈ S.Hs, (ψ₀.ψ₀ (h / S.M) : ℂ) * (starRingEnd ℂ) (ρ h) *
    ((2 * Real.pi * h * S.Y : ℝ) : ℂ) ^ (-(-3 / 2 + I * ξ)) *
      Mh S.ψ₁ S.ψ₂ S.X S.K h (-3 / 2 + I * ξ)

/-- `Bᴿ(ρ, τ) = (X/K) Y^(-1/2) (1/2π) ∫ G_τ(w) D(ρ, ξ) dξ`. -/
noncomputable def Brem (ρ : ℕ → ℂ) (τ : ℝ) : ℂ :=
  (S.Bk : ℂ) * ((1 / (2 * Real.pi) : ℂ) * ∫ ξ : ℝ, Gt τ (-3 / 2 + I * ξ) * S.Dsum ψ₀ ρ ξ)

theorem continuous_cpow_line {P : ℝ} (hP : 0 < P) :
    Continuous (fun ξ : ℝ => (P : ℂ) ^ (-(-3 / 2 + I * ξ))) :=
  Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hP.ne'))

theorem norm_cpow_line {P : ℝ} (hP : 0 < P) (ξ : ℝ) :
    ‖(P : ℂ) ^ (-(-3 / 2 + I * ξ))‖ = P ^ (3 / 2 : ℝ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hP]
  congr 1; simp; norm_num

/-- The integrand of the remainder for a single `h` is integrable. -/
theorem integrable_rem_h (hB : BesselAssumptions) (τ : ℝ) {h : ℝ} (hh : 0 < h) :
    Integrable (fun ξ : ℝ => Gt τ (-3 / 2 + I * ξ) *
      ((2 * Real.pi * h * S.Y : ℝ) : ℂ) ^ (-(-3 / 2 + I * ξ)) *
        Mh S.ψ₁ S.ψ₂ S.X S.K h (-3 / 2 + I * ξ)) := by
  have hP : 0 < 2 * Real.pi * h * S.Y := by have := S.Y_pos; positivity
  have hG := integrable_Gt hB τ
  have hdom := hG.norm.mul_const ((2 * Real.pi * h * S.Y) ^ (3 / 2 : ℝ) * (2 * S.C₀ ^ 2))
  have hc1 : Continuous fun ξ : ℝ => Gt τ (-3 / 2 + I * ξ) :=
    continuous_Gt_line.comp (f := fun ξ : ℝ => (τ, ξ)) (by fun_prop)
  have hc2 := continuous_cpow_line hP
  have hc3 : Continuous fun ξ : ℝ => Mh S.ψ₁ S.ψ₂ S.X S.K h (-3 / 2 + I * ξ) :=
    (S.continuous_Mh_w h).comp (by fun_prop)
  refine hdom.mono' ((hc1.mul hc2).mul hc3).aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  · rw [norm_mul, norm_mul, norm_cpow_line hP]
    have h1 := S.norm_Mh_le' h (w := -3 / 2 + I * ξ) (by simp; norm_num)
    calc ‖Gt τ (-3 / 2 + I * ξ)‖ * (2 * Real.pi * h * S.Y) ^ (3 / 2 : ℝ) *
          ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (-3 / 2 + I * ξ)‖
        ≤ ‖Gt τ (-3 / 2 + I * ξ)‖ * (2 * Real.pi * h * S.Y) ^ (3 / 2 : ℝ) * (2 * S.C₀ ^ 2) := by
          gcongr
      _ = _ := by ring

/-- **`B` on `𝒥₁`**: `B = B⁺ + B⁻ + Bᴿ` for real `τ ≠ 0`. -/
theorem B_eq_J1 (hB : BesselAssumptions) (ρ : ℕ → ℂ) {τ : ℝ} (hτ : τ ≠ 0) :
    S.B ψ₀ ρ τ = S.Bmain ψ₀ ρ τ + S.Bmain ψ₀ ρ (-τ) + S.Brem ψ₀ ρ τ := by
  rw [S.B_eq]
  have hY := S.Y_pos
  set c : ℕ → ℂ := fun h => (ψ₀.ψ₀ (h / S.M) : ℂ) * (starRingEnd ℂ) (ρ h) with hc
  set R : ℕ → ℝ → ℂ := fun h ξ => Gt τ (-3 / 2 + I * ξ) *
    ((2 * Real.pi * h * S.Y : ℝ) : ℂ) ^ (-(-3 / 2 + I * ξ)) *
      Mh S.ψ₁ S.ψ₂ S.X S.K h (-3 / 2 + I * ξ) with hR
  have hPsi : ∀ h ∈ S.Hs, PsiH S.ψ₁ S.ψ₂ S.X S.K S.Y h τ =
      (1 / 2 : ℂ) * Complex.Gamma (I * τ) * ((Real.pi * h * S.Y : ℝ) : ℂ) ^ (-(I * τ)) *
          Mh S.ψ₁ S.ψ₂ S.X S.K h (I * τ) +
        (1 / 2 : ℂ) * Complex.Gamma (-(I * τ)) * ((Real.pi * h * S.Y : ℝ) : ℂ) ^ (I * τ) *
          Mh S.ψ₁ S.ψ₂ S.X S.K h (-(I * τ)) +
        (1 / (2 * Real.pi) : ℂ) * ∫ ξ : ℝ, R h ξ := by
    intro h hh
    have h1 : (0 : ℝ) < h := by exact_mod_cast (S.le_of_mem_Hs hh).1
    exact PsiH_J1 hB S.hyp.smooth₁ S.hyp.supp₁ S.hyp.smooth₂.continuous S.hyp.supp₂ hY h1 hτ
  have hRint : ∀ h ∈ S.Hs, Integrable (R h) := by
    intro h hh
    have h1 : (0 : ℝ) < h := by exact_mod_cast (S.le_of_mem_Hs hh).1
    exact S.integrable_rem_h hB τ h1
  rw [Finset.sum_congr rfl (fun h hh => by
    rw [show (ψ₀.ψ₀ (h / S.M) : ℂ) * (starRingEnd ℂ) (ρ h) * PsiH S.ψ₁ S.ψ₂ S.X S.K S.Y h τ =
      c h * PsiH S.ψ₁ S.ψ₂ S.X S.K S.Y h τ by simp only [hc], hPsi h hh])]
  have hrem : ∑ h ∈ S.Hs, c h * ((1 / (2 * Real.pi) : ℂ) * ∫ ξ : ℝ, R h ξ) =
      (1 / (2 * Real.pi) : ℂ) * ∫ ξ : ℝ, Gt τ (-3 / 2 + I * ξ) * S.Dsum ψ₀ ρ ξ := by
    have h1 : ∀ h ∈ S.Hs, c h * ((1 / (2 * Real.pi) : ℂ) * ∫ ξ : ℝ, R h ξ) =
        (1 / (2 * Real.pi) : ℂ) * ∫ ξ : ℝ, c h * R h ξ := by
      intro h _
      rw [integral_const_mul]; ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum,
      ← integral_finsetSum _ (fun h hh => (hRint h hh).const_mul (c h))]
    congr 1
    congr 1; ext ξ
    simp only [Setup.Dsum, hR, hc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _; ring
  unfold Bmain Brem
  rw [← hrem]
  have e : I * ((-τ : ℝ) : ℂ) = -(I * τ) := by push_cast; ring
  rw [e, neg_neg]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  congr 1
  all_goals (apply Finset.sum_congr rfl; intro h _; simp only [hc]; ring)

/-! ### Majorants on `𝒥₁` -/

/-- The majorant `m⁺` of `|B⁺(ρ, τ)|²` (for `|τ| ≥ 1`). -/
noncomputable def mMain (ρ : ℕ → ℂ) (τ : ℝ) : ℝ :=
  S.Bk ^ 2 * (7 / 4) / Real.cosh (Real.pi * τ) * ‖∑ h ∈ S.Hs, ρ h * S.phiT ψ₀ τ h‖ ^ 2

theorem norm_sum_phiT (ρ : ℕ → ℂ) (τ : ℝ) :
    ‖∑ h ∈ S.Hs, (ψ₀.ψ₀ (h / S.M) : ℂ) * (starRingEnd ℂ) (ρ h) *
        ((Real.pi * h * S.Y : ℝ) : ℂ) ^ (-(I * τ)) * Mh S.ψ₁ S.ψ₂ S.X S.K h (I * τ)‖ =
      ‖∑ h ∈ S.Hs, ρ h * S.phiT ψ₀ τ h‖ := by
  rw [← RCLike.norm_conj (∑ h ∈ S.Hs, ρ h * S.phiT ψ₀ τ h)]
  congr 1
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro h _
  simp only [phiT, map_mul, RCLike.conj_conj]
  ring

theorem normSq_Bmain_le (ρ : ℕ → ℂ) {τ : ℝ} (hτ : 1 ≤ |τ|) :
    ‖S.Bmain ψ₀ ρ τ‖ ^ 2 ≤ S.mMain ψ₀ ρ τ := by
  unfold Bmain mMain
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg S.Bk_pos.le,
    S.norm_sum_phiT]
  have hΓ := norm_Gamma_I_mul_sq_le hτ
  have hc := Real.cosh_pos (Real.pi * τ)
  have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [h2]
  have e : (S.Bk * (1 / 2 * ‖Complex.Gamma (I * τ)‖ * ‖∑ h ∈ S.Hs, ρ h * S.phiT ψ₀ τ h‖)) ^ 2 =
      S.Bk ^ 2 * (1 / 4) * ‖Complex.Gamma (I * τ)‖ ^ 2 * ‖∑ h ∈ S.Hs, ρ h * S.phiT ψ₀ τ h‖ ^ 2 := by
    ring
  rw [e]
  have hB2 : 0 ≤ S.Bk ^ 2 * (1 / 4) := by positivity
  have hs2 : 0 ≤ ‖∑ h ∈ S.Hs, ρ h * S.phiT ψ₀ τ h‖ ^ 2 := sq_nonneg _
  calc S.Bk ^ 2 * (1 / 4) * ‖Complex.Gamma (I * τ)‖ ^ 2 * ‖∑ h ∈ S.Hs, ρ h * S.phiT ψ₀ τ h‖ ^ 2
      ≤ S.Bk ^ 2 * (1 / 4) * (7 / Real.cosh (Real.pi * τ)) *
          ‖∑ h ∈ S.Hs, ρ h * S.phiT ψ₀ τ h‖ ^ 2 := by gcongr
    _ = S.Bk ^ 2 * (7 / 4) / Real.cosh (Real.pi * τ) * ‖∑ h ∈ S.Hs, ρ h * S.phiT ψ₀ τ h‖ ^ 2 := by
        field_simp

/-- `c₂ = ∫ (1 + |ξ|)^(-2) dξ`. -/
noncomputable def c₂ : ℝ := ∫ ξ : ℝ, (1 + |ξ|) ^ (-(2 : ℝ))

theorem integrable_one_add_abs_rpow {r : ℝ} (hr : 1 < r) :
    Integrable (fun ξ : ℝ => (1 + |ξ|) ^ (-r)) := by
  have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := r) (by simpa using hr)
  simpa [Real.norm_eq_abs] using this

theorem c₂_nonneg : 0 ≤ c₂ := integral_nonneg fun ξ => by positivity

/-- The majorant `mᴿ` of `|Bᴿ(ρ, τ)|²`. -/
noncomputable def mRem (ρ : ℕ → ℂ) (τ : ℝ) : ℝ :=
  S.Bk ^ 2 * (1 / (4 * Real.pi ^ 2)) * c₂ *
    ∫ ξ : ℝ, (1 + |ξ|) ^ 2 * ‖Gt τ (-3 / 2 + I * ξ)‖ ^ 2 * ‖S.Dsum ψ₀ ρ ξ‖ ^ 2

theorem continuous_Dsum (ρ : ℕ → ℂ) : Continuous (S.Dsum ψ₀ ρ) := by
  unfold Dsum
  apply continuous_finsetSum _ fun h hh => ?_
  have hP : 0 < 2 * Real.pi * (h : ℝ) * S.Y := by
    have := (S.le_of_mem_Hs hh).1
    have : (0 : ℝ) < h := by exact_mod_cast this
    have := S.Y_pos
    positivity
  exact (continuous_const.mul (continuous_cpow_line hP)).mul
    ((S.continuous_Mh_w h).comp (by fun_prop))

/-- `|D(ρ, ξ)|² ≤ 2M ∑|ρ(h)|² ((4πMY)^(3/2) C₆ (1+|ξ|)^(-6))²` given the decay of `M_h`. -/
theorem norm_Dsum_sq_le {C6 : ℝ} (hC6 : 0 ≤ C6)
    (hM6 : ∀ h ∈ S.Hs, ∀ ξ : ℝ,
      ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (-3 / 2 + I * ξ)‖ ≤ C6 * (1 + |ξ|) ^ (-(6 : ℝ)))
    (ρ : ℕ → ℂ) (ξ : ℝ) :
    ‖S.Dsum ψ₀ ρ ξ‖ ^ 2 ≤ 2 * S.M * (∑ h ∈ S.Hs, ‖ρ h‖ ^ 2) *
      ((4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ) * C6 * (1 + |ξ|) ^ (-(6 : ℝ))) ^ 2 := by
  set b : ℝ := (4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ) * C6 * (1 + |ξ|) ^ (-(6 : ℝ)) with hb
  have hM0 := S.M_pos
  have hY0 := S.Y_pos
  have hb0 : 0 ≤ b := by have := Real.pi_pos; positivity
  have h1 : ‖S.Dsum ψ₀ ρ ξ‖ ≤ ∑ h ∈ S.Hs, b * ‖ρ h‖ := by
    unfold Dsum
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h hh => ?_)
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, RCLike.norm_conj]
    by_cases h0 : ψ₀.ψ₀ (h / S.M) = 0
    · rw [h0, abs_zero, zero_mul, zero_mul, zero_mul]; positivity
    · have hlt := S.lt_of_ψ₀_ne_zero ψ₀ h0
      have hh0 : (0 : ℝ) < h := by linarith [S.M_pos]
      have hP : 0 < 2 * Real.pi * (h : ℝ) * S.Y := by have := S.Y_pos; positivity
      rw [norm_cpow_line hP]
      have e1 : |ψ₀.ψ₀ (h / S.M)| ≤ 1 := by
        rw [abs_of_nonneg (ψ₀.nonneg _)]; exact ψ₀.le_one _
      have e2 : (2 * Real.pi * h * S.Y) ^ (3 / 2 : ℝ) ≤ (4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ) := by
        apply Real.rpow_le_rpow hP.le _ (by norm_num)
        have := S.Y_pos; have := Real.pi_pos
        nlinarith [hlt.2]
      have e3 := hM6 h hh ξ
      calc |ψ₀.ψ₀ (h / S.M)| * ‖ρ h‖ * (2 * Real.pi * h * S.Y) ^ (3 / 2 : ℝ) *
            ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (-3 / 2 + I * ξ)‖
          ≤ 1 * ‖ρ h‖ * (4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ) * (C6 * (1 + |ξ|) ^ (-(6 : ℝ))) := by
            gcongr
        _ = b * ‖ρ h‖ := by rw [hb]; ring
  have h2 : (∑ h ∈ S.Hs, b * ‖ρ h‖) ^ 2 ≤ (S.Hs).card * ∑ h ∈ S.Hs, (b * ‖ρ h‖) ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq S.Hs (fun _ => (1 : ℝ)) (fun h => b * ‖ρ h‖)
    simpa using this
  have h3 : ∑ h ∈ S.Hs, (b * ‖ρ h‖) ^ 2 = b ^ 2 * ∑ h ∈ S.Hs, ‖ρ h‖ ^ 2 := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro h _; ring
  have h4 := S.card_Hs_le
  have h5 : 0 ≤ b ^ 2 * ∑ h ∈ S.Hs, ‖ρ h‖ ^ 2 := by positivity
  have h6 : ‖S.Dsum ψ₀ ρ ξ‖ ^ 2 ≤ (∑ h ∈ S.Hs, b * ‖ρ h‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [h3] at h2
  have h7 : ((S.Hs).card : ℝ) * (b ^ 2 * ∑ h ∈ S.Hs, ‖ρ h‖ ^ 2) ≤
      2 * S.M * (b ^ 2 * ∑ h ∈ S.Hs, ‖ρ h‖ ^ 2) := mul_le_mul_of_nonneg_right h4 h5
  nlinarith

theorem one_add_abs_rpow_mul (ξ a b : ℝ) :
    (1 + |ξ|) ^ a * (1 + |ξ|) ^ b = (1 + |ξ|) ^ (a + b) :=
  (Real.rpow_add (by positivity) a b).symm

/-- The integrand of `mᴿ` is integrable. -/
theorem integrable_mRem {C6 CG : ℝ} (hC6 : 0 ≤ C6)
    (hM6 : ∀ h ∈ S.Hs, ∀ ξ : ℝ,
      ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (-3 / 2 + I * ξ)‖ ≤ C6 * (1 + |ξ|) ^ (-(6 : ℝ)))
    {τ : ℝ} (hG : ∀ ξ : ℝ, ‖Gt τ (-3 / 2 + I * ξ)‖ ≤ CG) (ρ : ℕ → ℂ) :
    Integrable (fun ξ : ℝ => (1 + |ξ|) ^ 2 * ‖Gt τ (-3 / 2 + I * ξ)‖ ^ 2 *
      ‖S.Dsum ψ₀ ρ ξ‖ ^ 2) := by
  set A : ℝ := CG ^ 2 * (2 * S.M * (∑ h ∈ S.Hs, ‖ρ h‖ ^ 2) *
    ((4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ) * C6) ^ 2) with hA
  have hdom := (integrable_one_add_abs_rpow (r := 10) (by norm_num)).const_mul A
  have hc1 : Continuous fun ξ : ℝ => Gt τ (-3 / 2 + I * ξ) :=
    continuous_Gt_line.comp (f := fun ξ : ℝ => (τ, ξ)) (by fun_prop)
  have hmeas : Continuous (fun ξ : ℝ => (1 + |ξ|) ^ 2 * ‖Gt τ (-3 / 2 + I * ξ)‖ ^ 2 *
      ‖S.Dsum ψ₀ ρ ξ‖ ^ 2) := by
    have := S.continuous_Dsum ψ₀ ρ
    fun_prop
  refine hdom.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  have hG0 : 0 ≤ CG := (norm_nonneg _).trans (hG 0)
  have h1 := pow_le_pow_left₀ (norm_nonneg _) (hG ξ) 2
  have h2 := S.norm_Dsum_sq_le ψ₀ hC6 hM6 ρ ξ
  have hpos : 0 < 1 + |ξ| := by positivity
  have e : (1 + |ξ|) ^ 2 * ((1 + |ξ|) ^ (-(6 : ℝ))) ^ 2 = (1 + |ξ|) ^ (-(10 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le,
      one_add_abs_rpow_mul]
    norm_num
  calc (1 + |ξ|) ^ 2 * ‖Gt τ (-3 / 2 + I * ξ)‖ ^ 2 * ‖S.Dsum ψ₀ ρ ξ‖ ^ 2
      ≤ (1 + |ξ|) ^ 2 * CG ^ 2 * (2 * S.M * (∑ h ∈ S.Hs, ‖ρ h‖ ^ 2) *
          ((4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ) * C6 * (1 + |ξ|) ^ (-(6 : ℝ))) ^ 2) := by
        gcongr
    _ = A * ((1 + |ξ|) ^ 2 * ((1 + |ξ|) ^ (-(6 : ℝ))) ^ 2) := by rw [hA]; ring
    _ = A * (1 + |ξ|) ^ (-(10 : ℝ)) := by rw [e]

theorem normSq_Brem_le {C6 CG : ℝ} (hC6 : 0 ≤ C6)
    (hM6 : ∀ h ∈ S.Hs, ∀ ξ : ℝ,
      ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (-3 / 2 + I * ξ)‖ ≤ C6 * (1 + |ξ|) ^ (-(6 : ℝ)))
    {τ : ℝ} (hG : ∀ ξ : ℝ, ‖Gt τ (-3 / 2 + I * ξ)‖ ≤ CG) (ρ : ℕ → ℂ) :
    ‖S.Brem ψ₀ ρ τ‖ ^ 2 ≤ S.mRem ψ₀ ρ τ := by
  set f : ℝ → ℂ := fun ξ => Gt τ (-3 / 2 + I * ξ) * S.Dsum ψ₀ ρ ξ with hf
  have hint := S.integrable_mRem ψ₀ hC6 hM6 hG ρ
  have hc1 : Continuous fun ξ : ℝ => Gt τ (-3 / 2 + I * ξ) :=
    continuous_Gt_line.comp (f := fun ξ : ℝ => (τ, ξ)) (by fun_prop)
  have hfc : Continuous f := hc1.mul (S.continuous_Dsum ψ₀ ρ)
  -- weighted Cauchy–Schwarz
  have hw : Integrable (fun ξ : ℝ => (1 + |ξ|) ^ (-(2 : ℝ))) :=
    integrable_one_add_abs_rpow (by norm_num)
  have hinvc : Continuous fun ξ : ℝ => (1 + |ξ|)⁻¹ := by
    apply Continuous.inv₀ (by fun_prop)
    intro ξ; positivity
  have hcs := setIntegral_mul_le_sqrt (μ := volume) (S := univ)
    (f := fun ξ : ℝ => (1 + |ξ|)⁻¹) (g := fun ξ => (1 + |ξ|) * ‖f ξ‖)
    (fun ξ => by positivity) (fun ξ => by positivity)
    hinvc.aestronglyMeasurable
    (Continuous.aestronglyMeasurable (by fun_prop))
    (by
      refine (hw.congr (Eventually.of_forall fun ξ => ?_)).integrableOn
      simp only
      rw [Real.rpow_neg (by positivity), inv_pow]; norm_num)
    (by
      refine (hint.congr (Eventually.of_forall fun ξ => ?_)).integrableOn
      simp only [hf]
      rw [norm_mul]; ring)
  simp only [Measure.restrict_univ] at hcs
  have hnorm : ∫ ξ : ℝ, (1 + |ξ|)⁻¹ * ((1 + |ξ|) * ‖f ξ‖) = ∫ ξ : ℝ, ‖f ξ‖ := by
    congr 1; ext ξ
    have hpos : 0 < 1 + |ξ| := by positivity
    rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
  have hw2 : ∫ ξ : ℝ, ((1 + |ξ|)⁻¹) ^ 2 = c₂ := by
    unfold c₂; congr 1; ext ξ
    rw [Real.rpow_neg (by positivity), inv_pow]; norm_num
  have hg2 : ∫ ξ : ℝ, ((1 + |ξ|) * ‖f ξ‖) ^ 2 =
      ∫ ξ : ℝ, (1 + |ξ|) ^ 2 * ‖Gt τ (-3 / 2 + I * ξ)‖ ^ 2 * ‖S.Dsum ψ₀ ρ ξ‖ ^ 2 := by
    congr 1; ext ξ; simp only [hf]; rw [norm_mul]; ring
  rw [hnorm, hw2, hg2] at hcs
  have h1 : ‖∫ ξ : ℝ, f ξ‖ ≤ ∫ ξ : ℝ, ‖f ξ‖ := norm_integral_le_integral_norm _
  have hI0 : 0 ≤ ∫ ξ : ℝ, (1 + |ξ|) ^ 2 * ‖Gt τ (-3 / 2 + I * ξ)‖ ^ 2 * ‖S.Dsum ψ₀ ρ ξ‖ ^ 2 :=
    integral_nonneg fun ξ => by positivity
  have h2 : ‖∫ ξ : ℝ, f ξ‖ ^ 2 ≤ c₂ *
      ∫ ξ : ℝ, (1 + |ξ|) ^ 2 * ‖Gt τ (-3 / 2 + I * ξ)‖ ^ 2 * ‖S.Dsum ψ₀ ρ ξ‖ ^ 2 := by
    have h3 := h1.trans hcs
    have h4 := pow_le_pow_left₀ (norm_nonneg _) h3 2
    rw [mul_pow, Real.sq_sqrt c₂_nonneg, Real.sq_sqrt hI0] at h4
    exact h4
  unfold Brem mRem
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg S.Bk_pos.le]
  have hpi : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hpi]
  have e : (S.Bk * (1 / (2 * Real.pi) * ‖∫ ξ : ℝ, Gt τ (-3 / 2 + I * ξ) * S.Dsum ψ₀ ρ ξ‖)) ^ 2 =
      S.Bk ^ 2 * (1 / (4 * Real.pi ^ 2)) * ‖∫ ξ : ℝ, f ξ‖ ^ 2 := by
    simp only [hf]; field_simp; ring
  rw [e]
  have hB0 : 0 ≤ S.Bk ^ 2 * (1 / (4 * Real.pi ^ 2)) := by positivity
  calc S.Bk ^ 2 * (1 / (4 * Real.pi ^ 2)) * ‖∫ ξ : ℝ, f ξ‖ ^ 2
      ≤ S.Bk ^ 2 * (1 / (4 * Real.pi ^ 2)) * (c₂ *
          ∫ ξ : ℝ, (1 + |ξ|) ^ 2 * ‖Gt τ (-3 / 2 + I * ξ)‖ ^ 2 * ‖S.Dsum ψ₀ ρ ξ‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h2 hB0
    _ = _ := by ring

end Setup

end Triples
